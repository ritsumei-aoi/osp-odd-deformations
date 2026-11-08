import OspOddDeformations.OspN.SourceIndependence

/-!
# The primitive `f_β`, for every `osp(N|2n)`

Paper Lemma 4.6, Theorem 4.7 and Corollary 4.8: `v` (the paper's `β̌`), `Z_β`,
`f_β = h̃ − ad Z_β`, the index rules, `Γ_β = δf_β`, and `T_β` intertwining, all at the
**coordinate** level (`OspMod F n`) — none of this needs `AB`/`Source` on its own,
only `bracket0`, `hTilde`, `Gamma`, `delta` (`OspN/Gamma.lean`). `delta_ad_eq_zero`
(below) is the one exception: it imports `OspN/SourceIndependence.lean`
for `iota0`/`base_realization`/`iota0_injective`.

**The one new ingredient**: `δ(ad Z) = 0` (paper Lemma 4.6) needs
super-Jacobi for `[·,·]₀`. Stated here as `delta_ad_eq_zero`. The route:
pull `bracket0` back to `AB F n`'s own associative product through `base_realization`,
generalized to a doubly-homogeneous pullback (`iota0_bracket0_homog`, below) rather
than a direct case-bash on `bracket0Basis`'s nine kinds, then use `iota0_injective`
to push the resulting (purely associative, sign-mechanical) identity back down to
`OspMod F n`.
-/

-- Toolchain port (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; restore
-- the pre-v4.34 type-transparency behaviour of `isDefEq` for this file.
set_option backward.isDefEq.respectTransparency.types false


namespace OspOddDeformations
namespace OspN

open Bmn (I J J_antisymm)

/-- `v t i`, the paper's `β̌_{t,i}`, defined by `Σ_t β̌_{t,i}J_{tu} = β_{u,i}` (paper eq. (4.7),
0-based: `β̌_{(k,false),i} = β_{(k,true),i}`, `β̌_{(k,true),i} = -β_{(k,false),i}`). -/
noncomputable def v (F : FermionIndex) (n : ℕ) (t : I n) (i : F.K) : Pmn F n :=
  match t with
  | (k, false) => beta F n (k, true) i
  | (k, true) => -beta F n (k, false) i

/-- `v`'s own defining property, `Σ_t β̌_{t,i}J_{tu} = β_{u,i}` — proved directly by
splitting `u = (m,false)`/`(m,true)` and picking out the single nonzero `J`-term
(`t=(m,true)`/`(m,false)` respectively), matching `v`'s own two-case definition. -/
theorem v_sum_J (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    ∑ t : I n, (J n t u : ℚ) • v F n t i = beta F n u i := by
  obtain ⟨m, b⟩ := u
  cases b with
  | false =>
    rw [Fintype.sum_eq_single (m, true)]
    · unfold v J; simp
    · intro t ht
      unfold J
      match t with
      | (k, false) => simp
      | (k, true) =>
        have : k ≠ m := by intro h; apply ht; rw [h]
        simp [this]
  | true =>
    rw [Fintype.sum_eq_single (m, false)]
    · unfold v J; simp
    · intro t ht
      unfold J
      match t with
      | (k, true) => simp
      | (k, false) =>
        have : k ≠ m := by intro h; apply ht; rw [h]
        simp [this]

/-- `v_sum_J` with the arguments of `J` swapped, via `J_antisymm` — the form actually
needed by `fBeta_L`/`fBeta_F`/`fBeta_S`, whose own `bracket0Basis` cross terms produce
`J n w t`/`J n u t` (boson first), not `J n t u`. -/
theorem v_sum_J_neg (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    ∑ t : I n, (J n u t : ℚ) • v F n t i = -beta F n u i := by
  rw [show (∑ t : I n, (J n u t : ℚ) • v F n t i)
      = ∑ t : I n, (-(J n t u : ℚ)) • v F n t i from by
    apply Finset.sum_congr rfl; intro t _; rw [J_antisymm u t]]
  rw [show (∑ t : I n, (-(J n t u : ℚ)) • v F n t i)
      = -∑ t : I n, (J n t u : ℚ) • v F n t i from by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro t _; rw [neg_smul]]
  rw [v_sum_J]

/-- `Z_β = 2 Σ_{t,i} β̌_{t,i} F_{t,i*}` (paper eq. (4.8)). -/
noncomputable def Zbeta (F : FermionIndex) (n : ℕ) : OspMod F n :=
  (2 : ℚ) • ∑ t : I n, ∑ i : F.K, (v F n t i) • eN (Fof t (F.dual i))

/-- `ad Z`, the adjoint action of a (not necessarily homogeneous) coordinate element on
`OspMod F n`, via `bracket0`. -/
noncomputable def ad {F : FermionIndex} {n : ℕ} (Z : OspMod F n) : OspMod F n → OspMod F n :=
  fun x => bracket0 Z x

/-- `f_β = h̃ − ad Z_β`. -/
noncomputable def fBeta (F : FermionIndex) (n : ℕ) : OspMod F n → OspMod F n :=
  fun x => hTilde x - ad (Zbeta F n) x

/-- `coefAB` is multiplicative: `c ↦ algebraMap c ᵍ⊗ₜ 1` is literally
`GradedTensorProduct.includeLeftRingHom ∘ algebraMap`, a ring hom. -/
theorem coefAB_mul (F : FermionIndex) (n : ℕ) (c1 c2 : Pmn F n) :
    coefAB F n c1 * coefAB F n c2 = coefAB F n (c1 * c2) := by
  unfold coefAB
  rw [show ((algebraMap (Pmn F n) (R F n) c1 : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n) : AB F n)
      = GradedTensorProduct.includeLeftRingHom (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
          (algebraMap (Pmn F n) (R F n) c1) from rfl,
    show ((algebraMap (Pmn F n) (R F n) c2 : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n) : AB F n)
      = GradedTensorProduct.includeLeftRingHom (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
          (algebraMap (Pmn F n) (R F n) c2) from rfl,
    ← map_mul, map_mul (algebraMap (Pmn F n) (R F n)),
    show (GradedTensorProduct.includeLeftRingHom (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
        (algebraMap (Pmn F n) (R F n) c1 * algebraMap (Pmn F n) (R F n) c2) : AB F n)
      = ((algebraMap (Pmn F n) (R F n) c1 * algebraMap (Pmn F n) (R F n) c2 : R F n)
          ᵍ⊗ₜ[ℚ] (1 : A0 F n) : AB F n) from rfl]

/-- `coefAB` values commute with each other: `Pmn F n`'s own commutativity, pushed
through `coefAB_mul`. -/
theorem coefAB_comm_coefAB (F : FermionIndex) (n : ℕ) (c1 c2 : Pmn F n) :
    coefAB F n c1 * coefAB F n c2 = coefAB F n c2 * coefAB F n c1 := by
  rw [coefAB_mul, coefAB_mul, mul_comm c1 c2]

/-- The pure-algebra identity underlying `iota0_bracket0_homog`'s own per-basis-pair
term: given `C` central against `D` and `W`, and `D` central against `V`, the product
`C*(D*(W*V-s•(V*W)))` regroups to `C*W*(D*V) - s•((D*V)*(C*W))`. -/
theorem cdwv_identity {F : FermionIndex} {n : ℕ} (C D W V : AB F n) (s : ℚ)
    (hCD : C * D = D * C) (hDW : D * W = W * D) (hCV : C * V = V * C) :
    C * (D * (W * V - s • (V * W))) = C * W * (D * V) - s • ((D * V) * (C * W)) := by
  rw [mul_sub, mul_smul_comm, mul_sub, mul_smul_comm]
  congr 1
  · calc C * (D * (W * V)) = C * D * W * V := by rw [← mul_assoc, ← mul_assoc]
      _ = C * (D * W) * V := by rw [mul_assoc C D W]
      _ = C * (W * D) * V := by rw [hDW]
      _ = C * W * D * V := by rw [← mul_assoc]
      _ = C * W * (D * V) := by rw [mul_assoc]
  · congr 1
    calc C * (D * (V * W)) = C * D * V * W := by rw [← mul_assoc, ← mul_assoc]
      _ = D * C * V * W := by rw [hCD]
      _ = D * (C * V) * W := by rw [mul_assoc D C V]
      _ = D * (V * C) * W := by rw [hCV]
      _ = D * V * C * W := by rw [← mul_assoc]
      _ = D * V * (C * W) := by rw [mul_assoc]

/-- **`base_realization`, doubly linearized**: `bracket0 x y` against TWO
parity-homogeneous general elements (not basis points), pushed through `iota0` —
generalizes `iota0_bracket0_eN_right_homog`/`_left_homog` (`SourceTensor.lean`, which
fix one side to a literal `eN Y`) to both sides general. Needed for `delta_ad_eq_zero`'s
own doubly-nested `bracket0`, where neither the inner nor outer argument is a bare
basis point. Proved by unfolding `bracket0`'s own double sum, collapsing each
`(i,j)`-term via `base_realization` and `cdwv_identity`. -/
theorem iota0_bracket0_homog {F : FermionIndex} {n : ℕ} (p q : ZMod 2) (x y : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → parity Z = p)
    (hy : ∀ Z : OspBasis F n, y Z ≠ 0 → parity Z = q) :
    iota0 F n (bracket0 x y)
      = iota0 F n x * iota0 F n y - gsign p q • (iota0 F n y * iota0 F n x) := by
  unfold bracket0
  rw [iota0_sum]
  have hterm : ∀ i : OspBasis F n,
      iota0 F n (∑ j : OspBasis F n, (x i * y j) • bracket0Basis i j)
      = coefAB F n (x i) * X0 F n i * iota0 F n y
        - gsign p q • (iota0 F n y * (coefAB F n (x i) * X0 F n i)) := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi, coefAB_zero, iota0_zero]
    · have hpi : parity i = p := hx i hxi
      rw [iota0_sum]
      have hinner : ∀ j : OspBasis F n,
          iota0 F n ((x i * y j) • bracket0Basis i j)
          = coefAB F n (x i) * X0 F n i * (coefAB F n (y j) * X0 F n j)
            - gsign p q • ((coefAB F n (y j) * X0 F n j) * (coefAB F n (x i) * X0 F n i)) := by
        intro j
        by_cases hyj : y j = 0
        · simp [hyj, coefAB_zero, iota0_zero]
        · have hqj : parity j = q := hy j hyj
          have hbr := base_realization F n i j
          unfold scomm at hbr
          rw [show ((x i * y j) • bracket0Basis i j : OspMod F n)
              = (x i) • ((y j) • bracket0Basis i j) from (smul_smul _ _ _).symm,
            iota0_smul_coefAB, iota0_smul_coefAB, ← hbr, hpi, hqj]
          exact cdwv_identity (coefAB F n (x i)) (coefAB F n (y j)) (X0 F n i) (X0 F n j)
            (gsign p q) (coefAB_comm_coefAB F n (x i) (y j)) (coefAB_comm_X0 F n (y j) i)
            (coefAB_comm_X0 F n (x i) j)
      rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_sub_distrib]
      congr 1
      · rw [← Finset.mul_sum]; rfl
      · rw [← Finset.smul_sum]
        congr 1
        rw [← Finset.sum_mul]; rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_mul]; rfl
  · rw [← Finset.smul_sum]
    congr 1
    rw [← Finset.mul_sum]; rfl

/-- A basis point `eN Y` is trivially homogeneous of its own parity. -/
theorem eN_homog {F : FermionIndex} {n : ℕ} (Y : OspBasis F n) :
    ∀ Z : OspBasis F n, (eN Y : OspMod F n) Z ≠ 0 → parity Z = parity Y := by
  intro Z hZ
  by_contra hne
  apply hZ
  unfold eN
  rw [ite_eq_right (fun h => hne (by rw [h]))]

/-- `bracket0`'s own parity-additivity, for a general homogeneous left argument against
a basis point on the right: `bracket0Basis_degree`'s own fact, summed over `z`'s basis
decomposition. Needed since `delta_ad_eq_zero`'s doubly-nested `bracket0` produces an
inner `bracket0 Z (eN X)` that is itself a general (not basis-vector) `OspMod` element,
which `iota0_bracket0_homog`'s own hypotheses require to be homogeneous. -/
theorem bracket0_homog_right {F : FermionIndex} {n : ℕ} (pz : ZMod 2) (z : OspMod F n)
    (hz : ∀ W : OspBasis F n, z W ≠ 0 → parity W = pz) (Y : OspBasis F n) :
    ∀ k : OspBasis F n, (bracket0 z (eN Y) : OspMod F n) k ≠ 0 → parity k = pz + parity Y := by
  intro k hk
  rw [bracket0_eN_right] at hk
  by_contra hne
  apply hk
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [ospMod_smul_apply]
  by_cases hzi : z i = 0
  · simp [hzi]
  · have hpi : parity i = pz := hz i hzi
    by_cases hbik : bracket0Basis i Y k = 0
    · simp [hbik]
    · exact absurd (hpi ▸ bracket0Basis_degree i Y k hbik) hne

/-- **`δ(ad Z) = 0` at a fixed basis pair `X,Y`** — the substantive content of
`delta_ad_eq_zero`. `iota0_injective` reduces the goal to showing `iota0` of
`deltaBasis (ad Z) X Y` vanishes; `iota0_bracket0_homog`, applied twice per term (once
for the outer `bracket0`, once for the inner `bracket0 Z (eN X)`/`bracket0 Z (eN Y)`,
using `bracket0_homog_right`/`bracket0Basis_degree` to supply the needed homogeneity),
expands all three `deltaBasis`-terms into an explicit combination of the six
noncommuting products of `w := iota0 Z`, `A := X0 X`, `B := X0 Y`, with `gsign`
coefficients. Case-splitting `parity X`/`parity Y` over `ZMod 2`'s two values reduces
every `gsign` to a concrete `±1`, at which point the six-term combination is a genuine
associative-ring identity (the *formal* super-Jacobi identity, needing only
associativity), closed by `noncomm_ring`. -/
theorem delta_ad_eq_zero_basis {F : FermionIndex} {n : ℕ} (Z : OspMod F n)
    (hZodd : ∀ k : OspBasis F n, Z k ≠ 0 → parity k = 1) (X Y : OspBasis F n) :
    deltaBasis (ad Z) X Y = 0 := by
  apply iota0_injective
  rw [iota0_zero]
  unfold deltaBasis ad
  rw [iota0_sub, iota0_add, iota0_smul_rat]
  rw [show (bracket0 (eN X) (eN Y) : OspMod F n) = bracket0Basis X Y from bracket0_eN_eN X Y]
  have hZX := bracket0_homog_right 1 Z hZodd X
  have hZY := bracket0_homog_right 1 Z hZodd Y
  have hXY := bracket0Basis_degree X Y
  have heNX := eN_homog X
  have heNY := eN_homog Y
  rw [iota0_bracket0_homog (1 + parity X) (parity Y) (bracket0 Z (eN X)) (eN Y) hZX heNY,
    iota0_bracket0_homog 1 (parity X) Z (eN X) hZodd heNX, iota0_eN, iota0_eN,
    iota0_bracket0_homog (parity X) (1 + parity Y) (eN X) (bracket0 Z (eN Y)) heNX hZY,
    iota0_bracket0_homog 1 (parity Y) Z (eN Y) hZodd heNY, iota0_eN, iota0_eN,
    iota0_bracket0_homog 1 (parity X + parity Y) Z (bracket0Basis X Y) hZodd hXY]
  have hbrXY := base_realization F n X Y
  unfold scomm at hbrXY
  rw [← hbrXY]
  have h0 : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  set w := iota0 F n Z with hw
  set A := X0 F n X with hA
  set B := X0 F n Y with hB
  clear_value w A B
  clear hZodd hZX hZY hXY heNX heNY hbrXY hw hA hB
  rcases h0 (parity X) with hX' | hX' <;> rcases h0 (parity Y) with hY' | hY' <;>
    rw [hX', hY'] <;>
    simp only [gsign_00, gsign_01, gsign_10, gsign_11, h11, zero_add, add_zero,
      one_smul, neg_one_smul] <;>
    noncomm_ring

/-- **The new ingredient**: `δ(ad Z) = 0` for `Z` odd (paper Lemma 4.6)
— needs super-Jacobi for `bracket0`. `hZodd` states
`Z ∈ 𝔤_1̄ ⊗ P`: every basis coefficient of `Z` is supported only on the `F`-kind (odd)
sector. Proved at each basis pair by `delta_ad_eq_zero_basis`; `delta`'s own outer
`Σ_X Σ_Y` structure means the general-element case needs no further linearization
argument, just `Finset.sum_eq_zero` twice. -/
theorem delta_ad_eq_zero {F : FermionIndex} {n : ℕ} (Z : OspMod F n)
    (hZodd : ∀ k : OspBasis F n, Z k ≠ 0 → parity k = 1) (x y : OspMod F n) :
    delta (ad Z) x y = 0 := by
  unfold delta
  apply Finset.sum_eq_zero
  intro X _
  apply Finset.sum_eq_zero
  intro Y _
  rw [delta_ad_eq_zero_basis Z hZodd X Y, smul_zero]

/-- `Z_β` is odd (supported only on `F`-kind basis elements): immediate from `Zbeta`'s
own definition as a sum of `eN (Fof _ _)` terms — every `L`-kind and `S`-kind
coefficient is forced to `0` since `eN (Fof t (F.dual i))` vanishes there, leaving only
the `F`-kind case, where `parity = 1` by `parity`'s own definition. -/
theorem Zbeta_odd (F : FermionIndex) (n : ℕ) :
    ∀ k : OspBasis F n, Zbeta F n k ≠ 0 → parity k = 1 := by
  intro k hk
  rcases k with p | s | f
  · exfalso; apply hk; obtain ⟨⟨a, b⟩, h⟩ := p; unfold Zbeta; simp
  · exfalso; apply hk; obtain ⟨⟨a, b⟩, h⟩ := s; unfold Zbeta; simp
  · rfl

/-- `bracket0` against a basis point of `F`-kind on the left, `Lof u w` on the right —
`bracketLF`'s own symmetry in its first two arguments (`bracketLF u v w k = bracketLF v
u w k`, immediate from its own formula) makes the sign uniform regardless of which way
`Lof`'s internal sort picked. -/
theorem bracket0_Fof_Lof {F : FermionIndex} {n : ℕ} (t : I n) (k : F.K) (u w : I n) :
    bracket0 (eN (Fof t k) : OspMod F n) (eN (Lof u w)) = -bracketLF u w t k := by
  unfold Lof
  split
  · rw [bracket0_eN_eN]; rfl
  · rw [bracket0_eN_eN]
    change -bracketLF _ _ t k = _
    rw [show bracketLF w u t k = bracketLF u w t k from by
      unfold bracketLF; rw [add_comm]]

/-- **`f_β(L) = 0`** (paper Theorem 4.7). Expands `h̃(eN(Lof u w))` (`hTildeBasis_Lof`)
against `bracket0(Z_β, eN(Lof u w))`: `Z_β`'s own double sum collapses termwise via
`bracket0_Fof_Lof`, then the inner boson sum collapses via `v_sum_J_neg` (`Σ_t
β̌_{t,i}J_{w,t} = -β_{w,i}`, using `J`'s antisymmetry), leaving exactly `h̃`'s own
formula after reindexing `i ↦ i*`. -/
theorem fBeta_L (F : FermionIndex) (n : ℕ) (u w : I n) :
    fBeta F n (eN (Lof u w)) = 0 := by
  unfold fBeta ad
  rw [sub_eq_zero, hTilde_eN, hTildeBasis_Lof]
  unfold Zbeta
  rw [bracket0_smul_left_rat, bracket0_sum_left]
  have hstep1 : ∀ t : I n,
      bracket0 (∑ i : F.K, v F n t i • eN (Fof t (F.dual i))) (eN (Lof u w) : OspMod F n)
      = ∑ i : F.K, ((-(1 / 2 * J n w t : ℚ) • v F n t i) • eN (Fof u (F.dual i))
          + (-(1 / 2 * J n u t : ℚ) • v F n t i) • eN (Fof w (F.dual i))) := by
    intro t
    rw [bracket0_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [bracket0_smul_left, bracket0_Fof_Lof]
    unfold bracketLF
    rw [smul_neg, smul_add]
    rw [smul_comm (v F n t i), smul_assoc, smul_comm (v F n t i) (1 / 2 * J n u t : ℚ),
      smul_assoc]
    rw [neg_smul, neg_smul]
    abel
  rw [Finset.sum_congr rfl (fun t _ => hstep1 t)]
  rw [show (∑ t : I n, ∑ i : F.K, ((-(1 / 2 * J n w t : ℚ) • v F n t i) • eN (Fof u (F.dual i))
          + (-(1 / 2 * J n u t : ℚ) • v F n t i) • eN (Fof w (F.dual i)) : OspMod F n))
      = ∑ i : F.K, ((∑ t : I n, -(1 / 2 * J n w t : ℚ) • v F n t i) • eN (Fof u (F.dual i))
          + (∑ t : I n, -(1 / 2 * J n u t : ℚ) • v F n t i) • eN (Fof w (F.dual i))) from by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_smul]]
  have hA : ∀ i : F.K,
      (∑ t : I n, -(1 / 2 * J n w t : ℚ) • v F n t i) = (1 / 2 : ℚ) • beta F n w i := by
    intro i
    rw [show (∑ t : I n, -(1 / 2 * J n w t : ℚ) • v F n t i)
        = -(1 / 2 : ℚ) • ∑ t : I n, (J n w t : ℚ) • v F n t i from by
      rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro t _; module]
    rw [v_sum_J_neg]
    module
  have hB : ∀ i : F.K,
      (∑ t : I n, -(1 / 2 * J n u t : ℚ) • v F n t i) = (1 / 2 : ℚ) • beta F n u i := by
    intro i
    rw [show (∑ t : I n, -(1 / 2 * J n u t : ℚ) • v F n t i)
        = -(1 / 2 : ℚ) • ∑ t : I n, (J n u t : ℚ) • v F n t i from by
      rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro t _; module]
    rw [v_sum_J_neg]
    module
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hA i, hB i] :
    ∀ i ∈ Finset.univ, ((∑ t : I n, -(1 / 2 * J n w t : ℚ) • v F n t i) • eN (Fof u (F.dual i))
        + (∑ t : I n, -(1 / 2 * J n u t : ℚ) • v F n t i) • eN (Fof w (F.dual i))
        : OspMod F n)
      = ((1 / 2 : ℚ) • beta F n w i) • eN (Fof u (F.dual i))
        + ((1 / 2 : ℚ) • beta F n u i) • eN (Fof w (F.dual i)))]
  rw [Finset.smul_sum]
  have hsimp : ∀ i : F.K, ((2 : ℚ) • (((1 / 2 : ℚ) • beta F n w i) • eN (Fof u (F.dual i))
      + ((1 / 2 : ℚ) • beta F n u i) • eN (Fof w (F.dual i))) : OspMod F n)
      = beta F n w i • eN (Fof u (F.dual i)) + beta F n u i • eN (Fof w (F.dual i)) := by
    intro i
    rw [smul_add]
    rw [smul_assoc, smul_smul, smul_assoc, smul_smul]
    norm_num
  rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
  rw [show (∑ i : F.K, (beta F n w i • eN (Fof u (F.dual i))
        + beta F n u i • eN (Fof w (F.dual i)) : OspMod F n))
      = ∑ i : F.K, beta F n w i • eN (Fof u (F.dual i))
        + ∑ i : F.K, beta F n u i • eN (Fof w (F.dual i)) from Finset.sum_add_distrib]
  have hRA : (∑ i : F.K, beta F n w i • eN (Fof u (F.dual i)) : OspMod F n)
      = ∑ i : F.K, beta F n w (F.dual i) • eN (Fof u i) := by
    have h := sum_dual (M := OspMod F n) (fun x => beta F n w (F.dual x) • eN (Fof u x))
    simp only [F.dual_dual] at h
    exact h
  have hRB : (∑ i : F.K, beta F n u i • eN (Fof w (F.dual i)) : OspMod F n)
      = ∑ i : F.K, beta F n u (F.dual i) • eN (Fof w i) := by
    have h := sum_dual (M := OspMod F n) (fun x => beta F n u (F.dual x) • eN (Fof w x))
    simp only [F.dual_dual] at h
    exact h
  rw [hRA, hRB]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

/-- `bracket0` against two basis points of `F`-kind — direct from `bracket0_eN_eN`. -/
theorem bracket0_Fof_Fof {F : FermionIndex} {n : ℕ} (t : I n) (k' : F.K) (w : I n) (k : F.K) :
    bracket0 (eN (Fof t k') : OspMod F n) (eN (Fof w k)) = bracketFF t k' w k := by
  rw [bracket0_eN_eN]; rfl

/-- `F.g` against a dualized index — `F.dual`'s own involutivity, `F.dual_dual`, turned
into the Kronecker delta on the un-dualized index. -/
theorem g_dual_delta (F : FermionIndex) (i k : F.K) :
    F.g (F.dual i) k = if k = i then (1:ℚ) else 0 := by
  unfold FermionIndex.g
  rw [F.dual_dual]

/-- **The `F`-index rule, `f_β(F_{w,k}) = -Σ_t β̌_{t,k} L_{tw}`** (paper Theorem 4.7).
`bracket0(Z_β, eN(Fof w k))` splits, via `bracketFF`, into a "`Sof`-part" that collapses
(`v_sum_J`) to exactly cancel `h̃`'s own `Fof`-formula (`hTildeBasis_Fof`), and a
"`Lof`-part" that collapses (`g_dual_delta` picking out the single `i = k` term) to
exactly the target sum, up to the leading sign from `fBeta`'s own `h̃ x - ad(Z_β) x`. -/
theorem fBeta_F (F : FermionIndex) (n : ℕ) (w : I n) (k : F.K) :
    fBeta F n (eN (Fof w k)) = -∑ t : I n, (v F n t k) • eN (Lof t w) := by
  unfold fBeta ad
  rw [hTilde_eN, hTildeBasis_Fof]
  unfold Zbeta
  rw [bracket0_smul_left_rat, bracket0_sum_left]
  have hstep1 : ∀ t : I n,
      bracket0 (∑ i : F.K, v F n t i • eN (Fof t (F.dual i))) (eN (Fof w k) : OspMod F n)
      = ∑ i : F.K, (v F n t i • ((1 / 4 * J n t w : ℚ) • Sof (F.dual i) k)
          + v F n t i • ((1 / 2 : ℚ) • ((if k = i then (1:ℚ) else 0) • eN (Lof t w)))) := by
    intro t
    rw [bracket0_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [bracket0_smul_left, bracket0_Fof_Fof]
    unfold bracketFF
    rw [smul_add]
    congr 1
    congr 1
    rw [g_dual_delta]
    module
  rw [Finset.sum_congr rfl (fun t _ => hstep1 t)]
  rw [show (∑ t : I n, ∑ i : F.K, (v F n t i • ((1 / 4 * J n t w : ℚ) • Sof (F.dual i) k)
          + v F n t i • ((1 / 2 : ℚ) • ((if k = i then (1:ℚ) else 0) • eN (Lof t w))) : OspMod F n))
      = (∑ t : I n, ∑ i : F.K, ((1 / 4 * J n t w : ℚ) • v F n t i) • Sof (F.dual i) k)
        + (∑ t : I n, ∑ i : F.K, ((1 / 2 * (if k = i then (1:ℚ) else 0) : ℚ) • v F n t i)
            • eN (Lof t w)) from by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [smul_smul, smul_comm (v F n t i) (1 / 4 * J n t w : ℚ), smul_assoc,
      smul_comm (v F n t i) (1 / 2 * (if k = i then (1:ℚ) else 0) : ℚ), smul_assoc]]
  have sofPart : (∑ t : I n, ∑ i : F.K, ((1 / 4 * J n t w : ℚ) • v F n t i) • Sof (F.dual i) k
        : OspMod F n)
      = (1 / 4 : ℚ) • ∑ j : F.K, beta F n w j • Sof (F.dual j) k := by
    rw [Finset.sum_comm]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (∑ t : I n, ((1 / 4 * J n t w : ℚ) • v F n t i) • Sof (F.dual i) k : OspMod F n)
        = (∑ t : I n, (1 / 4 * J n t w : ℚ) • v F n t i) • Sof (F.dual i) k from
      (Finset.sum_smul).symm]
    rw [show (∑ t : I n, (1 / 4 * J n t w : ℚ) • v F n t i)
        = (1/4:ℚ) • ∑ t : I n, (J n t w : ℚ) • v F n t i from by
      rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro t _; module]
    rw [v_sum_J, smul_assoc]
  have lofPart : (∑ t : I n, ∑ i : F.K, ((1 / 2 * (if k = i then (1:ℚ) else 0) : ℚ) • v F n t i)
        • eN (Lof t w) : OspMod F n)
      = (1 / 2 : ℚ) • ∑ t : I n, v F n t k • eN (Lof t w) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [show (∑ i : F.K, ((1 / 2 * (if k = i then (1:ℚ) else 0) : ℚ) • v F n t i)
          • eN (Lof t w) : OspMod F n)
        = (∑ i : F.K, (1 / 2 * (if k = i then (1:ℚ) else 0) : ℚ) • v F n t i) • eN (Lof t w) from
      (Finset.sum_smul).symm]
    rw [show (∑ i : F.K, (1 / 2 * (if k = i then (1:ℚ) else 0) : ℚ) • v F n t i)
        = (1/2:ℚ) • v F n t k from by
      rw [Fintype.sum_eq_single k]
      · simp
      · intro i hi; simp [Ne.symm hi]]
    rw [smul_assoc]
  rw [sofPart, lofPart]
  rw [smul_add, smul_smul, smul_smul]
  norm_num

/-- **The `S`-index rule, `f_β(S_{ij}) = 2Σ_t(β̌_{t,j}F_{t,i} - β̌_{t,i}F_{t,j})`** (paper
Theorem 4.7). `hTilde_Sof` gives `h̃(S_{ij}) = 0`, so this is `-bracket0(Z_β, S_{ij})`.
`bracket0_Fof_Sof` expands `Z_β`'s own double sum into `bracketSF`, whose `F.g` values
against a dualized index collapse (`F.dual`'s injectivity, via `F.dual_dual`) to pick out
the single `l = i` / `l = j` terms. -/
theorem fBeta_S (F : FermionIndex) (n : ℕ) (i j : F.K) :
    fBeta F n (Sof i j)
      = (2 : ℚ) • ∑ t : I n, ((v F n t j) • eN (Fof t i) - (v F n t i) • eN (Fof t j)) := by
  unfold fBeta ad
  rw [hTilde_Sof]
  unfold Zbeta
  rw [bracket0_smul_left_rat, bracket0_sum_left]
  have hstep1 : ∀ t : I n,
      bracket0 (∑ l : F.K, v F n t l • eN (Fof t (F.dual l))) (Sof i j : OspMod F n)
      = ∑ l : F.K, v F n t l • (-((if l = j then (1:ℚ) else 0) • eN (Fof t i)
          - (if l = i then (1:ℚ) else 0) • eN (Fof t j))) := by
    intro t
    rw [bracket0_sum_left]
    apply Finset.sum_congr rfl
    intro l _
    rw [bracket0_smul_left, bracket0_Fof_Sof]
    unfold bracketSF
    congr 1
    rw [show (F.g j (F.dual l) : ℚ) = (if l = j then (1:ℚ) else 0) from by
        unfold FermionIndex.g
        by_cases h : l = j
        · subst h; simp
        · have : F.dual l ≠ F.dual j := fun hc =>
            h (by have := congrArg F.dual hc; simpa [F.dual_dual] using this)
          simp [this, h]
      , show (F.g i (F.dual l) : ℚ) = (if l = i then (1:ℚ) else 0) from by
        unfold FermionIndex.g
        by_cases h : l = i
        · subst h; simp
        · have : F.dual l ≠ F.dual i := fun hc =>
            h (by have := congrArg F.dual hc; simpa [F.dual_dual] using this)
          simp [this, h]]
  rw [Finset.sum_congr rfl (fun t _ => hstep1 t)]
  have hcollapse : ∀ t : I n,
      (∑ l : F.K, v F n t l • (-((if l = j then (1:ℚ) else 0) • eN (Fof t i)
          - (if l = i then (1:ℚ) else 0) • eN (Fof t j))) : OspMod F n)
      = v F n t i • eN (Fof t j) - v F n t j • eN (Fof t i) := by
    intro t
    rw [show (∑ l : F.K, v F n t l • (-((if l = j then (1:ℚ) else 0) • eN (Fof t i)
          - (if l = i then (1:ℚ) else 0) • eN (Fof t j))) : OspMod F n)
        = ∑ l : F.K, ((if l = j then (1:ℚ) else 0) • (- v F n t l • eN (Fof t i))
            + (if l = i then (1:ℚ) else 0) • (v F n t l • eN (Fof t j))) from by
      apply Finset.sum_congr rfl; intro l _
      by_cases hlj : l = j <;> by_cases hli : l = i <;> simp_all]
    rw [Finset.sum_add_distrib]
    rw [Fintype.sum_eq_single j (f := fun l => (if l = j then (1:ℚ) else 0)
        • (- v F n t l • eN (Fof t i) : OspMod F n))
      (by intro l hl; simp [hl])]
    rw [Fintype.sum_eq_single i (f := fun l => (if l = i then (1:ℚ) else 0)
        • (v F n t l • eN (Fof t j) : OspMod F n))
      (by intro l hl; simp [hl])]
    simp
    abel
  rw [Finset.sum_congr rfl (fun t _ => hcollapse t)]
  rw [zero_sub, ← smul_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  abel

/-- `bracket0` distributes over subtraction on the left — `bracket0_add_left` plus
`bracket0_neg_left` via `sub_eq_add_neg`. -/
theorem bracket0_sub_left {F : FermionIndex} {n : ℕ} (x y z : OspMod F n) :
    bracket0 (x - y) z = bracket0 x z - bracket0 y z := by
  rw [sub_eq_add_neg, bracket0_add_left, bracket0_neg_left, sub_eq_add_neg]

/-- `bracket0` distributes over subtraction on the right. -/
theorem bracket0_sub_right {F : FermionIndex} {n : ℕ} (x y z : OspMod F n) :
    bracket0 x (y - z) = bracket0 x y - bracket0 x z := by
  rw [sub_eq_add_neg, bracket0_add_right, bracket0_neg_right, sub_eq_add_neg]

/-- **`Γ_β = δf_β`** (paper Theorem 4.7, its main clause). Since `f_β = h̃ − ad Z_β`
pointwise, `deltaBasis`'s own three-term formula (built from `bracket0` and one direct
application of `f`) distributes over that subtraction termwise (`bracket0_sub_left`/
`_right`, `smul_sub`), giving `δh̃ = δf_β + δ(ad Z_β)` at the basis level, hence at the
general level after summing. `δ(ad Z_β) = 0` by `delta_ad_eq_zero`,
using `Zbeta_odd` for the oddness side condition.
Combined with `Gamma_eq_delta_hTilde` (already proved), `Γ = δh̃ = δf_β + 0 = δf_β`. -/
theorem Gamma_eq_delta_fBeta (F : FermionIndex) (n : ℕ) (x y : OspMod F n) :
    Gamma x y = delta (fBeta F n) x y := by
  have hZ : delta (ad (Zbeta F n)) x y = 0 := delta_ad_eq_zero (Zbeta F n) (Zbeta_odd F n) x y
  have hsplit : delta hTilde x y = delta (fBeta F n) x y + delta (ad (Zbeta F n)) x y := by
    unfold delta
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← smul_add]
    congr 1
    unfold deltaBasis fBeta ad
    rw [bracket0_sub_left, bracket0_sub_right, smul_sub]
    abel
  rw [Gamma_eq_delta_hTilde, hsplit, hZ, add_zero]

/-- `f_β`'s `κ`-extension, `(f_β)_R`, mirroring `hTildeR`. -/
noncomputable def fBetaR {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n :=
  iotaR (fBeta F n (falsePart r)) + kappaEmbed (-(fBeta F n (truePart r)))

/-- `T_β = id + κ(f_β)_R`, mirroring `TBeta`. -/
noncomputable def TBetaF {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n :=
  r + kappaMulR (fBetaR r)

/-! ## `T_β` intertwines (paper Corollary 4.8) — "the argument is the same" as `T`'s own
`intertwining` (`OspN/Kappa.lean`), with `f_β` in place of `h̃`. Every supporting lemma
below mirrors a `Kappa.lean` original one-for-one (`TBeta_*` ↦ `TBetaF_*`, `hTilde` ↦
`fBeta F n`), using `Gamma_eq_delta_fBeta` in place of `Gamma_eq_delta_hTilde_basis` at
the one substantive step. The **same** `bracketRBeta`/`bracketRBetaBasis` (built from
`GammaBasis`, `Kappa.lean`) is intertwined — only the primitive changes, from `h̃` to
`f_β`, since both are shown to satisfy `Γ = δ(·)`. -/

/-- `Gamma` at a basis pair collapses to `GammaBasis`, mirroring `bracketR_eR_eR`. -/
theorem Gamma_eN_eN {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) :
    Gamma (eN X : OspMod F n) (eN Y) = GammaBasis X Y := by
  unfold Gamma
  rw [Finset.sum_eq_single X]
  · rw [Finset.sum_eq_single Y]
    · simp [eN]
    · intro b _ hb
      have : eN Y b = 0 := by unfold eN; rw [ite_eq_right hb]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ Y) h
  · intro b _ hb
    have : eN X b = 0 := by unfold eN; rw [ite_eq_right hb]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ X) h

/-- `delta f` at a basis pair collapses to `deltaBasis f`, mirroring `bracketR_eR_eR`. -/
theorem delta_eN_eN {F : FermionIndex} {n : ℕ} (f : OspMod F n → OspMod F n) (X Y : OspBasis F n) :
    delta f (eN X : OspMod F n) (eN Y) = deltaBasis f X Y := by
  unfold delta
  rw [Finset.sum_eq_single X]
  · rw [Finset.sum_eq_single Y]
    · simp [eN]
    · intro b _ hb
      have : eN Y b = 0 := by unfold eN; rw [ite_eq_right hb]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ Y) h
  · intro b _ hb
    have : eN X b = 0 := by unfold eN; rw [ite_eq_right hb]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ X) h

/-- **`Γ_β = δf_β`, basis level**, the analogue of `Gamma_eq_delta_hTilde_basis` for
`f_β`: specializes the general `Gamma_eq_delta_fBeta` to a basis pair. -/
theorem Gamma_eq_delta_fBeta_basis (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    GammaBasis X Y = deltaBasis (fBeta F n) X Y := by
  have h := Gamma_eq_delta_fBeta F n (eN X) (eN Y)
  rwa [Gamma_eN_eN, delta_eN_eN] at h

theorem fBeta_zero (F : FermionIndex) (n : ℕ) : fBeta F n (0 : OspMod F n) = 0 := by
  unfold fBeta ad; rw [hTilde_zero, bracket0_zero_right, sub_zero]

theorem fBeta_add (F : FermionIndex) (n : ℕ) (x y : OspMod F n) :
    fBeta F n (x + y) = fBeta F n x + fBeta F n y := by
  unfold fBeta ad
  rw [hTilde_add, bracket0_add_right]
  abel

theorem fBeta_smul (F : FermionIndex) (n : ℕ) (c : Pmn F n) (x : OspMod F n) :
    fBeta F n (c • x) = c • fBeta F n x := by
  unfold fBeta ad
  rw [hTilde_smul, bracket0_smul_right, smul_sub]

theorem TBetaF_eq {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    TBetaF r = r + kappaEmbed (fBeta F n (falsePart r)) := by
  unfold TBetaF fBetaR
  rw [kappaMulR_add, kappaMulR_iotaR, kappaMulR_kappaEmbed, add_zero]

theorem falsePart_TBetaF {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    falsePart (TBetaF r) = falsePart r := by
  rw [TBetaF_eq, falsePart_add, falsePart_kappaEmbed, add_zero]

theorem TBetaF_zero {F : FermionIndex} {n : ℕ} : TBetaF (0 : RMod F n) = 0 := by
  have hfp0 : falsePart (0 : RMod F n) = 0 := by funext k; simp [falsePart]
  rw [TBetaF_eq, hfp0, fBeta_zero, kappaEmbed_zero, add_zero]

theorem TBetaF_add {F : FermionIndex} {n : ℕ} (r1 r2 : RMod F n) :
    TBetaF (r1 + r2) = TBetaF r1 + TBetaF r2 := by
  rw [TBetaF_eq, TBetaF_eq, TBetaF_eq, falsePart_add, fBeta_add, kappaEmbed_add]
  abel

theorem TBetaF_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (r : RMod F n) :
    TBetaF (c • r) = c • TBetaF r := by
  rw [TBetaF_eq, TBetaF_eq, falsePart_smul, fBeta_smul, kappaEmbed_smul, smul_add]

-- the `DecidableEq` instance is kept: removing it would change the statement
set_option linter.unusedDecidableInType false in
theorem TBetaF_sum {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → RMod F n) : TBetaF (∑ i ∈ s, f i) = ∑ i ∈ s, TBetaF (f i) := by
  induction s using Finset.induction with
  | empty => simp [TBetaF_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, TBetaF_add, ih, Finset.sum_insert ha]

-- the `DecidableEq` instance is kept: removing it would change the statement
set_option linter.unusedDecidableInType false in
theorem TBetaF_sum' {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → Pmn F n) (f : ι → RMod F n) :
    TBetaF (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • TBetaF (f i) := by
  induction s using Finset.induction with
  | empty => simp [TBetaF_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, TBetaF_add, TBetaF_smul, ih, Finset.sum_insert ha]

theorem TBetaF_eR_false {F : FermionIndex} {n : ℕ} (i : OspBasis F n) :
    TBetaF (eR ((i, false) : RBasis F n))
      = eR ((i, false) : RBasis F n) + kappaEmbed (fBeta F n (eN i)) := by
  rw [TBetaF_eq, falsePart_eR_false]

theorem TBetaF_eR_true {F : FermionIndex} {n : ℕ} (i : OspBasis F n) :
    TBetaF (eR ((i, true) : RBasis F n)) = eR ((i, true) : RBasis F n) := by
  rw [TBetaF_eq, falsePart_eR_true, fBeta_zero, kappaEmbed_zero, add_zero]

/-- The intertwining, basis level — mirrors `intertwining_basis` exactly, citing
`Gamma_eq_delta_fBeta_basis` in place of `Gamma_eq_delta_hTilde_basis` at the
substantive `(false,false)` case. -/
theorem intertwining_fBeta_basis {F : FermionIndex} {n : ℕ} (p q : RBasis F n) :
    bracketR (TBetaF (eR p)) (TBetaF (eR q)) = TBetaF (bracketRBeta (eR p) (eR q)) := by
  rcases p with ⟨i, bi⟩; rcases q with ⟨j, bj⟩
  cases bi <;> cases bj
  · -- (i,false),(j,false) -- the substantive case
    rw [TBetaF_eR_false, TBetaF_eR_false, bracketRBeta_eR_eR]
    show bracketR (eR ((i, false) : RBasis F n) + kappaEmbed (fBeta F n (eN i)))
        (eR ((j, false) : RBasis F n) + kappaEmbed (fBeta F n (eN j)))
      = TBetaF (bracketRBetaBasis (i, false) (j, false))
    rw [bracketR_add_left, bracketR_add_right, bracketR_add_right]
    rw [bracketR_eR_eR, bracketR_eR_false_kappaEmbed, bracketR_kappaEmbed_eR_false,
        bracketR_kappaEmbed_kappaEmbed, add_zero]
    simp only [bracketRBasis]
    set A := gsign (parity i) 1 • bracket0 (eN i) (fBeta F n (eN j)) with hA
    set B := bracket0 (fBeta F n (eN i)) (eN j) with hB
    have hfix : TBetaF (kappaEmbed (GammaBasis i j)) = kappaEmbed (GammaBasis i j) := by
      rw [TBetaF_eq, falsePart_kappaEmbed, fBeta_zero, kappaEmbed_zero, add_zero]
    simp only [bracketRBetaBasis]
    rw [TBetaF_add, TBetaF_eq, falsePart_iotaR, hfix]
    set Z := fBeta F n (bracket0Basis i j) with hZ
    rw [Gamma_eq_delta_fBeta_basis]
    unfold deltaBasis
    rw [bracket0_eN_eN, ← hB, ← hA, ← hZ]
    have key : kappaEmbed A + kappaEmbed B = kappaEmbed Z + kappaEmbed (B + A - Z) := by
      rw [← kappaEmbed_add, ← kappaEmbed_add]
      refine congrArg kappaEmbed ?_
      abel
    calc iotaR (bracket0Basis i j) + kappaEmbed A + kappaEmbed B
        = iotaR (bracket0Basis i j) + (kappaEmbed A + kappaEmbed B) := by abel
      _ = iotaR (bracket0Basis i j) + (kappaEmbed Z + kappaEmbed (B + A - Z)) := by rw [key]
      _ = iotaR (bracket0Basis i j) + kappaEmbed Z + kappaEmbed (B + A - Z) := by abel
  · -- (i,false),(j,true)
    rw [TBetaF_eR_false, TBetaF_eR_true, bracketRBeta_eR_eR]
    show bracketR (eR ((i, false) : RBasis F n) + kappaEmbed (fBeta F n (eN i)))
        (eR ((j, true) : RBasis F n))
      = TBetaF (bracketRBetaBasis (i, false) (j, true))
    rw [bracketR_add_left, bracketR_eR_eR, bracketR_kappaEmbed_eR_true, add_zero]
    show bracketRBasis (i, false) (j, true) = TBetaF (bracketRBetaBasis (i, false) (j, true))
    change kappaEmbed (gsign (parity i) 1 • bracket0Basis i j)
      = TBetaF (kappaEmbed (gsign (parity i) 1 • bracket0Basis i j))
    rw [TBetaF_eq, falsePart_kappaEmbed, fBeta_zero, kappaEmbed_zero, add_zero]
  · -- (i,true),(j,false)
    rw [TBetaF_eR_true, TBetaF_eR_false, bracketRBeta_eR_eR]
    show bracketR (eR ((i, true) : RBasis F n))
        (eR ((j, false) : RBasis F n) + kappaEmbed (fBeta F n (eN j)))
      = TBetaF (bracketRBetaBasis (i, true) (j, false))
    rw [bracketR_add_right, bracketR_eR_eR, bracketR_eR_true_kappaEmbed, add_zero]
    show bracketRBasis (i, true) (j, false) = TBetaF (bracketRBetaBasis (i, true) (j, false))
    change kappaEmbed (bracket0Basis i j) = TBetaF (kappaEmbed (bracket0Basis i j))
    rw [TBetaF_eq, falsePart_kappaEmbed, fBeta_zero, kappaEmbed_zero, add_zero]
  · -- (i,true),(j,true)
    rw [TBetaF_eR_true, TBetaF_eR_true, bracketRBeta_eR_eR, bracketR_eR_eR]
    change (0 : RMod F n) = TBetaF (0 : RMod F n)
    rw [TBetaF_zero]

/-- **`T_β` intertwines** (paper Corollary 4.8), for **arbitrary** (not just basis)
elements — mirrors `intertwining` exactly, lifting `intertwining_fBeta_basis` by
`eR_decompose`. -/
theorem intertwining_fBeta {F : FermionIndex} {n : ℕ} (x y : RMod F n) :
    bracketR (TBetaF x) (TBetaF y) = TBetaF (bracketRBeta x y) := by
  have hLHS : bracketR (TBetaF x) (TBetaF y)
      = ∑ p : RBasis F n, ∑ q : RBasis F n,
          (x p * y q) • bracketR (TBetaF (eR p)) (TBetaF (eR q)) := by
    conv_lhs => rw [eR_decompose x, eR_decompose y]
    rw [TBetaF_sum', TBetaF_sum', bracketR_sum_left'']
    apply Finset.sum_congr rfl; intro p _
    rw [bracketR_sum_right'', Finset.smul_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [smul_smul]
  have hRHS : TBetaF (bracketRBeta x y)
      = ∑ p : RBasis F n, ∑ q : RBasis F n,
          (x p * y q) • bracketR (TBetaF (eR p)) (TBetaF (eR q)) := by
    unfold bracketRBeta
    rw [TBetaF_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [TBetaF_sum']
    apply Finset.sum_congr rfl; intro q _
    rw [← bracketRBeta_eR_eR p q]
    exact congrArg (fun z => (x p * y q) • z) (intertwining_fBeta_basis p q).symm
  rw [hLHS, hRHS]

end OspN
end OspOddDeformations
